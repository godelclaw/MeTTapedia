import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRadialSource
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRegularizedSourceBound

/-!
# Local domination of the actual radial stretching source

The contractive radial Fourier multiplier supplies a bound independent of
cutoff. The Fourier envelope is a local regularity resource, not a bound
derived from initial energy or a replacement for the signed dynamical budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityRadialSource

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeFourierPressureStrain PancakePeriodicVorticityEquation
open LocalLowDiffusionBudget LocalVorticityEighthMoment
open scoped Matrix.Norms.Elementwise
local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem norm_source_six_le (N : ℕ) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = PancakeBlockReality.coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    ‖source 6 N u‖ ≤ (9 * ∑' k, ‖strainCoeff u k‖) * meanEnergy u := by
  have hw := continuous_fullVorticity u hu
  have he : Integrable (energy u) :=
    (((hw.norm.pow 2).pow 4)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi := norm_integral_le_of_norm_le
    (f := fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 *
      VorticityRadialQuadratic.quadraticStretch N u x (fullVorticity u x))
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
    (mul_le_mul_of_nonneg_left (VorticityRegularizedSource.tsum_norm_strainCoeff_le u g hg hu)
      (by norm_num : (0 : ℝ) ≤ 9)) (meanEnergy_nonneg u)
  simpa only [mul_assoc] using h

end Mettapedia.FluidDynamics.NavierStokes.VorticityRadialSource
