import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalHelicityCenterSourceBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.HelicitySourceTests

/-!
# Exact-flow tests for the mixed-gradient and center-source estimates

The horizontal parallel family has zero advection, so its mixed cost equals
the sixth vorticity moment. The same identity holds along its full heat
evolution. This special equality is not imposed on general flows.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.MixedGradientTests

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail
open PancakeInfiniteFourierDerivative PancakeFourierTranslationCurve
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open LocalLowDiffusionBudget LocalAlignmentForcing
open HelicityAngularBudget CurlVorticitySource LocalWeightedDivCurl LocalMixedGradientBudget
open LocalHelicityCenterSourceBudget HelicitySourceTests ParallelHeatFlow

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem advection_parallel_eq_zero (a : Wavevector → ℂ) (ha : IsHorizontal a) (x : T3) :
    advection (fun q ↦ vertical (a q)) x = 0 := by
  have he : advectionCoeff (fun q ↦ vertical (a q)) = 0 := by
    funext q
    simp only [advectionCoeff, infiniteConvection_eq_zero ha, smul_zero, Pi.zero_apply]
  have hF : fullFourierField id (0 : FourierVelocity) = 0 := by
    have hm (q : Wavevector) : modeField q (0 : VelocityCoefficient) = 0 := by
      ext y i
      simp [modeField]
    change (∑' q : Wavevector, modeField q (0 : VelocityCoefficient)) = 0
    simp only [hm, tsum_zero]
  unfold advection
  rw [he, hF]
  exact map_zero _

theorem advection_heatCoefficients_eq_zero (ν : ℝ) (a : Wavevector →₀ ℂ)
    (ha : IsHorizontal a) (t : ℝ) (x : T3) : advection (coefficients ν a t) x = 0 := by
  rw [coefficients_eq_vertical_heatData]
  exact advection_parallel_eq_zero _ (heatData_horizontal ν a ha t) x

theorem mixedGradientCost_parallel_eq_sixthMoment (a : Wavevector →₀ ℂ)
    (ha : IsHorizontal a) (hr : ∀ q, a (-q) = conj (a q)) :
    mixedGradientCost (fun q ↦ vertical (a q)) = sixthMoment (fun q ↦ vertical (a q)) := by
  have hre (q : Wavevector) : vertical (a (-q)) = PancakeBlockReality.coefficientConjugate (vertical (a q)) := by
    rw [hr, vertical_conj]
  rw [mixedGradientCost_eq_add_flux _ (summable_initial_fourierMoment 3 a) (transverse ha) hre]
  simp only [weightedFlux, advection_parallel_eq_zero _ ha, PiLp.zero_apply,
    mul_zero, Finset.sum_const_zero, integral_zero, add_zero]

theorem mixedGradientCost_heatCoefficients_eq_sixthMoment (ν : ℝ) (a : Wavevector →₀ ℂ)
    (ha : IsHorizontal a) (hr : ∀ q, a (-q) = conj (a q)) (t : ℝ) :
    mixedGradientCost (coefficients ν a t) = sixthMoment (coefficients ν a t) := by
  rw [coefficients_eq_vertical_heatData]
  apply mixedGradientCost_parallel_eq_sixthMoment _ (heatData_horizontal ν a ha t)
  intro q
  simp only [heatData_apply, decayRate_neg, map_mul, Complex.conj_ofReal, hr]

theorem centerSource_parallel_eq_zero (δ : ℝ) (a : Wavevector →₀ ℂ)
    (ha : IsHorizontal a) (hr : ∀ q, a (-q) = conj (a q)) (x : T3) :
    centerSource δ (fun q ↦ vertical (a q)) x = 0 := by
  simp only [centerSource, source_parallel_eq_zero a ha hr, inner_zero_right, zero_div]

theorem centerStretchFeedback_parallel_eq_zero (δ : ℝ) (a : Wavevector →₀ ℂ)
    (ha : IsHorizontal a) (x : T3) : centerStretchFeedback δ (fun q ↦ vertical (a q)) x = 0 := by
  simp only [centerStretchFeedback, fullStrain_apply_vorticity_eq_zero a ha,
    inner_zero_right, mul_zero]

theorem weightedCenterSource_heatCoefficients_eq_zero (δ ν : ℝ) (a : Wavevector →₀ ℂ)
    (ha : IsHorizontal a) (hr : ∀ q, a (-q) = conj (a q)) (t : ℝ) :
    weightedCenterSource δ (coefficients ν a t) = 0 := by
  simp only [weightedCenterSource, centerSource, source_heatCoefficients_eq_zero ν a ha hr,
    inner_zero_right, zero_div, abs_zero, mul_zero, integral_zero]

end Mettapedia.FluidDynamics.NavierStokes.MixedGradientTests
