import Mettapedia.Analysis.UnitTorusQuarticSecondEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPolynomialDifferential

/-!
# A weighted second-derivative Bernstein estimate for real scalar polynomials

The fourth power has Fourier radius at most four times the original
radius. Its integrated coercivity converts the ordinary L2 Bernstein
estimate into a weighted derivative estimate with no support-cardinality
factor. The scalar projection and vector mixed-derivative transfers are
separate obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ScalarQuarticBernstein

open MeasureTheory Mettapedia.Analysis UnitTorusQuarticSecondEnergy
open PeriodicFourierTriad PancakeQuadraticFourierSupport FourierPolynomialRealAlgebra
open FourierPolynomialDifferential PancakeFourierTranslationCurve PancakeHaarTransportRate

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem hasRadius_derivative {a : FourierCoeff (Fin 3)} {R : ℝ}
    (ha : HasRadius a R) (j : Fin 3) : HasRadius (ParallelHeatFlow.derivativeCoeff a j) R :=
  fun q hq ↦ ha q (ParallelHeatFlow.support_derivativeCoeff_subset a j hq)

theorem integral_coordinateDerivative_sq_le (a : FourierCoeff (Fin 3)) (R : ℝ)
    (ha : HasRadius a R) (j : Fin 3) :
    (∫ x : T3, ‖fourierPolynomial (ParallelHeatFlow.derivativeCoeff a j) x‖ ^ 2) ≤
      (2 * Real.pi * R) ^ 2 * ∫ x : T3, ‖fourierPolynomial a x‖ ^ 2 := by
  exact (Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) ↦
    integral_nonneg (fun _ ↦ sq_nonneg _)) (Finset.mem_univ j)).trans
      (integral_gradient_sq_le a R ha)

def fourthPowerCoeff (a : FourierCoeff (Fin 3)) : FourierCoeff (Fin 3) :=
  productCoeff (productCoeff a a) (productCoeff a a)

theorem fourierPolynomial_fourthPowerCoeff (a : FourierCoeff (Fin 3)) (x : T3) :
    fourierPolynomial (fourthPowerCoeff a) x = fourierPolynomial a x ^ 4 := by
  simp only [fourthPowerCoeff, fourierPolynomial_productCoeff, ContinuousMap.mul_apply]
  ring

theorem hasRadius_fourthPower {a : FourierCoeff (Fin 3)} {R : ℝ} (ha : HasRadius a R) :
    HasRadius (fourthPowerCoeff a) (4 * R) := by
  have h := hasRadius_product (hasRadius_product ha ha) (hasRadius_product ha ha)
  simpa only [fourthPowerCoeff, show R + R + (R + R) = 4 * R by ring] using h

/-- The input and its two derivatives are identified by actual translation
derivatives. This is not a weighted estimate for an independent weight. -/
theorem integral_weightedSecond_sq_le (a : FourierCoeff (Fin 3)) (R : ℝ) (ha : HasRadius a R)
    (f v z : T3 → ℝ) (hf : Continuous f) (hv : Continuous v) (hz : Continuous z)
    (he : ∀ x, fourierPolynomial a x = (f x : ℂ)) (j : Fin 3)
    (hf' : ∀ x h, HasDerivAt (fun t ↦ f (x + coordinateShift j t)) (v (x + coordinateShift j h)) h)
    (hv' : ∀ x h, HasDerivAt (fun t ↦ v (x + coordinateShift j t)) (z (x + coordinateShift j h)) h) :
    (∫ x : T3, f x ^ 6 * z x ^ 2) ≤
      25 * (2 * Real.pi * R) ^ 2 * ∫ x : T3, f x ^ 6 * v x ^ 2 := by
  let b := ParallelHeatFlow.derivativeCoeff (fourthPowerCoeff a) j
  let c := ParallelHeatFlow.derivativeCoeff b j
  have hb (x : T3) : fourierPolynomial b x = (4 * f x ^ 3 * v x : ℝ) := by
    have hp := hasDerivAt_fourierPolynomial_shift (fourthPowerCoeff a) j x 0
    have hq := ((hf' x 0).fun_pow 4).ofReal_comp
    simp only [coordinateShift_zero, add_zero] at hp hq
    simp_rw [fourierPolynomial_fourthPowerCoeff, he, ← Complex.ofReal_pow] at hp
    exact hp.unique hq
  have hc (x : T3) : fourierPolynomial c x = (quarticSecond (f x) (v x) (z x) : ℂ) := by
    have hp := hasDerivAt_fourierPolynomial_shift b j x 0
    have hq := (hasDerivAt_quarticFirst (hf' x 0) (hv' x 0)).ofReal_comp
    simp only [coordinateShift_zero, add_zero] at hp hq
    simp_rw [hb] at hp
    exact hp.unique hq
  have hB := integral_coordinateDerivative_sq_le b (4 * R)
    (hasRadius_derivative (hasRadius_fourthPower ha) j) j
  change (∫ x : T3, ‖fourierPolynomial c x‖ ^ 2) ≤ _ at hB
  simp_rw [hc, hb, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hB
  have hfirst : (∫ x : T3, (4 * f x ^ 3 * v x) ^ 2) =
      16 * ∫ x : T3, f x ^ 6 * v x ^ 2 := by
    calc
      _ = ∫ x : T3, 16 * (f x ^ 6 * v x ^ 2) := integral_congr_ae
        (Filter.Eventually.of_forall (fun _ ↦ by ring))
      _ = _ := integral_const_mul _ _
  rw [hfirst] at hB
  have hW := UnitTorusQuarticSecondEnergy.integral_weightedSecond_sq_le f v z (coordinateShift j)
    hf hv hz (continuous_coordinateShift j) (coordinateShift_zero j) hf' hv'
  have hBW := mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 25 / 256)
  nlinarith only [hW, hBW]

end Mettapedia.FluidDynamics.NavierStokes.ScalarQuarticBernstein
