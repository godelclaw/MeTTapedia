import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalGaussianFourierBudget

/-! Sign, normalization, and finite-coefficient regressions for the Fourier gradient bridge. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianFourierBudgetAudit

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakeFourierTranslationCurve
open PeriodicFourierWeakDerivative PeriodicFourierProjection PancakeQuadraticFourierSupport
open FourierEllipticProductEnergy FourierEllipticProductCoefficients
open Mettapedia.Analysis.UnitTorusFourierEnergy Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "T3" => UnitAddTorus (Fin 3)

example (x : T3) : deriv (fun h : ℝ ↦ UnitAddTorus.mFourier 0 (x + coordinateShift 0 h)) 0 = 0 := by
  simpa only [Pi.zero_apply, Int.cast_zero, mul_zero, zero_mul] using
    (hasDerivAt_character_shift 0 0 x).deriv

/-- A negative frequency retains its sign in the physical derivative. -/
example (x : T3) :
    deriv (fun h : ℝ ↦ UnitAddTorus.mFourier ![-1, 0, 0] (x + coordinateShift 0 h)) 0 =
      -unitTorusDerivativePhase * UnitAddTorus.mFourier ![-1, 0, 0] x := by
  simpa using (hasDerivAt_character_shift ![-1, 0, 0] 0 x).deriv

example (q : Wavevector) : projectionCoeff (UnitAddTorus.mFourier q) {q} = Finsupp.single q 1 := by
  ext k
  simp only [projectionCoeff_apply, Finset.mem_singleton, mFourierCoeff_character,
    Finsupp.single_apply]
  by_cases h : k = q
  · simp [h]
  · simp [h, Ne.symm h]

/-- Frequencies (-1,2,0) cost 1+4 before multiplication by the squared torus phase. -/
example : coordinateEnergy (Finsupp.single (![-1, 2, 0] : Wavevector) (1 : ℂ)).support
    (Finsupp.single (![-1, 2, 0] : Wavevector) (1 : ℂ)) = 5 := by
  norm_num [coordinateEnergy, scalarEnergy, coordinateMultiplier, Fin.sum_univ_three]
  rfl

end Mettapedia.FluidDynamics.NavierStokes.GaussianFourierBudgetAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierWeakDerivative.integral_coordinateRate_mul_complex
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierWeakDerivative.hasDerivAt_character_shift
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierWeakDerivative.locallyLipschitz_character
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierWeakDerivative.mFourierCoeff_coordinateRate
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierGradientEnergy.memLp_coordinateRate
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierGradientEnergy.integrable_gradientSquare
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierGradientEnergy.coordinateEnergy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierGradientEnergy.gradientEnergy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProjection.projectionCoeff_apply
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProjection.support_projectionCoeff_subset
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProjection.fourierPolynomial_projectionCoeff
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProjection.coordinateEnergy_projectionCoeff
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProjection.exists_fourier_approximation_gradient_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGaussianFourierBudget.exists_local_gaussian_fourier_budget
