import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ScalarQuarticBernstein
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteVorticityTensor

/-!
# Weighted Bernstein bounds for all real projections of finite vorticity

The scalar polynomial is constructed from the actual curl coefficients.
The bound holds for every fixed real projection vector, not only coordinate
components. It does not yet supply the vector-valued or mixed-spatial-jet
estimate needed to absorb the complete projection-curvature cost.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteVorticityProjectedBernstein

open scoped RealInnerProductSpace
open MeasureTheory
open PeriodicFourierTriad PancakeQuadraticFourierSupport FourierPolynomialRealAlgebra
open FourierPolynomialDifferential FourierFiniteSupport FiniteVorticityTensor
open PancakeCurlOutputTail PancakeFrequencyProjectorCommutator
open PancakeFourierTranslationCurve LocalLowDiffusionBudget LocalSpatialVorticityJets
open LocalJointDiffusionBudget LocalAlignmentForcing

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def projectedCurlCoeff (P : Finset Wavevector) (u : FourierVelocity) (e : R3) : FourierCoeff (Fin 3) :=
  ∑ i : Fin 3, (e i : ℂ) • curlCoeff P u i

theorem fourierPolynomial_projectedCurlCoeff (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (e : R3) (x : T3) :
    fourierPolynomial (projectedCurlCoeff P u e) x = (⟪e, fullVorticity u x⟫ : ℂ) := by
  simp only [projectedCurlCoeff, Fin.sum_univ_three, fourierPolynomial_add,
    fourierPolynomial_smul, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    smul_eq_mul, fourierPolynomial_curlCoeff P u hs]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, mul_comm]

theorem hasRadius_projectedCurlCoeff (P : Finset Wavevector) (u : FourierVelocity)
    (R : ℝ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R) (e : R3) :
    HasRadius (projectedCurlCoeff P u e) R :=
  hasRadius_sum _ _ R (fun i _ ↦ hasRadius_smul (hasRadius_curlCoeff P u R hP i) _)

theorem integral_projected_second_sq_le (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (R : ℝ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (e : R3) (j : Fin 3) :
    (∫ x : T3, ⟪e, fullVorticity u x⟫ ^ 6 * ⟪e, fullCurlSecond u j x⟫ ^ 2) ≤
      25 * (2 * Real.pi * R) ^ 2 *
        ∫ x : T3, ⟪e, fullVorticity u x⟫ ^ 6 * ⟪e, fullCurlGradient u j x⟫ ^ 2 := by
  have hu3 := summable_fourierMoment P u hs 3
  apply ScalarQuarticBernstein.integral_weightedSecond_sq_le
    (projectedCurlCoeff P u e) R (hasRadius_projectedCurlCoeff P u R hP e)
    (fun x ↦ ⟪e, fullVorticity u x⟫) (fun x ↦ ⟪e, fullCurlGradient u j x⟫)
    (fun x ↦ ⟪e, fullCurlSecond u j x⟫)
    (continuous_const.inner (continuous_fullVorticity u (summable_fourierMoment P u hs 1)))
    (continuous_const.inner (LocalSquaredGapGradient.continuous_fullCurlGradient u j))
    (continuous_const.inner (LocalPairedDiffusion.continuous_fullCurlSecond u j))
    (fourierPolynomial_projectedCurlCoeff P u hs e) j
  · intro x h
    simpa only [inner_zero_left, zero_add, add_zero] using
      (hasDerivAt_const h e).inner ℝ (hasDerivAt_fullVorticity_shift u hu3 j x h)
  · intro x h
    simpa only [inner_zero_left, zero_add, add_zero] using
      (hasDerivAt_const h e).inner ℝ (hasDerivAt_fullCurlGradient_shift u hu3 j x h)

end Mettapedia.FluidDynamics.NavierStokes.FiniteVorticityProjectedBernstein
