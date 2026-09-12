import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRegularizedSource

/-!
# A cutoff-independent local majorant for the regularized stretching source

This bound justifies time convergence on a supplied smooth interval. Its
Fourier-envelope constant is not an a priori bound near a possible singular
time and is not used as a substitute for the signed remainder budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedSource

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeFourierPressureStrain PancakeFourierStrainGradient
open PancakePeriodicVorticityEquation FullStrainFourierSeries LocalLowDiffusionBudget
open PancakeFrequencyProjectorCommutator
open LocalVorticityEighthMoment
open scoped Matrix.Norms.Elementwise
local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem norm_strainCoeff_le_firstMoment (u : FourierVelocity) (q : Wavevector) :
    ‖strainCoeff u q‖ ≤ ‖unitTorusDerivativePhase‖ * fourierMoment 1 u q := by
  apply (norm_strainCoeff_le u q).trans
  unfold fourierMoment
  simp only [pow_one]
  nlinarith [norm_nonneg (coefficientVec (u q)), norm_nonneg (frequencyVec q),
    norm_nonneg unitTorusDerivativePhase]

theorem tsum_norm_strainCoeff_le (u : FourierVelocity) (g : Wavevector → ℝ)
    (hg : Summable g) (hu : ∀ q, fourierMoment 1 u q ≤ g q) :
    (∑' q, ‖strainCoeff u q‖) ≤ ‖unitTorusDerivativePhase‖ * ∑' q, g q := by
  have hu1 := hg.of_nonneg_of_le (fourierMoment_nonneg 1 u) hu
  have hs := (summable_norm_strainCoeff u hu1).tsum_le_tsum
    (fun q ↦ (norm_strainCoeff_le_firstMoment u q).trans
      (mul_le_mul_of_nonneg_left (hu q) (norm_nonneg _))) (hg.mul_left ‖unitTorusDerivativePhase‖)
  simpa only [tsum_mul_left] using hs

theorem norm_source_six_le (N : ℕ) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = PancakeBlockReality.coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    ‖source 6 N u‖ ≤ (9 * ∑' k, ‖strainCoeff u k‖) * meanEnergy u := by
  have hw := continuous_fullVorticity u hu
  have he : Integrable (energy u) :=
    (((hw.norm.pow 2).pow 4)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi := norm_integral_le_of_norm_le
    (f := fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 *
      VorticityRegularizedQuadratic.quadraticStretch N u x (fullVorticity u x))
    (he.const_mul (9 * ∑' k, ‖strainCoeff u k‖))
    (Filter.Eventually.of_forall (fun x : T3 ↦ by
      have h := mul_le_mul_of_nonneg_left
        (norm_quadraticStretch_le N u hu hr hd x (fullVorticity u x))
        (pow_nonneg (norm_nonneg (fullVorticity u x)) 6)
      simp only [norm_mul, norm_pow, norm_norm]
      apply h.trans_eq
      unfold energy
      ring))
  simpa only [source, meanEnergy, integral_const_mul] using hi

theorem norm_source_six_le_envelope (N : ℕ) (u : FourierVelocity) (g : Wavevector → ℝ)
    (hg : Summable g) (hu : ∀ q, fourierMoment 1 u q ≤ g q)
    (hr : ∀ k, u (-k) = PancakeBlockReality.coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    ‖source 6 N u‖ ≤ (9 * ‖unitTorusDerivativePhase‖ * ∑' q, g q) * meanEnergy u := by
  have hu1 := hg.of_nonneg_of_le (fourierMoment_nonneg 1 u) hu
  apply (norm_source_six_le N u hu1 hr hd).trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (tsum_norm_strainCoeff_le u g hg hu) (by norm_num : (0 : ℝ) ≤ 9))
    (meanEnergy_nonneg u)
  simpa only [mul_assoc] using h

end Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedSource
