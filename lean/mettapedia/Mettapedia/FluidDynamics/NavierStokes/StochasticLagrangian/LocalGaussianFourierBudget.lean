import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalGaussianGradientBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicFourierProjection

/-!
# Actual Gaussian patches and finite Fourier approximants with a common budget

For every positive localization tolerance and approximation error, the
actual strain/vorticity geometry supplies spatial patches and finite
Fourier polynomials. The total L2 error is small and the polynomial
gradient energy is bounded by the same physical density as the patches.
Exact coverage and line localization concern the spatial patches; they
are not falsely transferred pointwise through L2 convergence.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalGaussianFourierBudget

open scoped BigOperators
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakePeriodicVorticityEquation PancakeHigherDerivativeMoments
open PancakeQuadraticFourierSupport FourierEllipticProductEnergy
open LocalSquaredGapPressure LocalGaussianPressurePartition LocalGaussianGradientBudget
open AdaptiveGaussianLinePartition SpectralTiltFreezing PeriodicFourierProjection

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The spatial cover and its gradient budget are fixed before choosing
the Fourier approximation error. -/
theorem exists_local_gaussian_fourier_family (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (rho : ℝ) (hr : 0 < rho) :
    ∃ centers : Finset T3, centers.Nonempty ∧
      let tau := temperature centers.card rho
      let p := patch gamma chi modes u centers tau
      0 < tau ∧ (∀ i, Continuous (p i)) ∧
      (∀ x, (∑ i, p i x ^ 2) = localWeight gamma chi modes u x) ∧
      (∀ x, (∑ i, p i x ^ 2 *
        lineDistanceSq (localDirection chi modes u x) (localDirection chi modes u i.1)) ≤ rho ^ 2) ∧
      ∀ delta : ℝ, 0 < delta → ∃ c : ↑centers → FourierCoeff (Fin 3),
        (∑ i, ∫ x : T3, ‖fourierPolynomial (c i) x - (p i x : ℂ)‖ ^ 2) < delta ∧
        ‖unitTorusDerivativePhase‖ ^ 2 * (∑ i, coordinateEnergy (c i).support (c i)) ≤
          ∫ x : T3, gradientDensity gamma chi modes u rho tau x := by
  obtain ⟨centers, hc, ht, hp, hmass, hline, _, _, _, hbudget⟩ :=
    exists_local_gaussian_gradient_budget gamma hg chi modes u hu rho hr
  let tau := temperature centers.card rho
  let p := patch gamma chi modes u centers tau
  refine ⟨centers, hc, ht, hp, hmass, hline, ?_⟩
  intro delta hd
  have hL (i : ↑centers) := locallyLipschitz_patch gamma hg chi modes u
    (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu) centers hc tau i
  obtain ⟨c, herr, hgrad⟩ := exists_fourier_approximation_gradient_budget p hp hL delta hd
  have hid : (∑ i, ∫ x : T3, PeriodicFourierGradientEnergy.gradientSquare (p i) x) =
      ∫ x : T3, patchGradientSquare gamma chi modes u centers tau x := by
    rw [← integral_finsetSum _ (fun i _ ↦
      PeriodicFourierGradientEnergy.integrable_gradientSquare (p i) (hp i) (hL i))]
    apply integral_congr_ae
    filter_upwards [] with x
    exact Finset.sum_comm
  exact ⟨c, herr, hgrad.trans (hid.le.trans hbudget)⟩

theorem exists_local_gaussian_fourier_budget (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (rho delta : ℝ) (hr : 0 < rho) (hd : 0 < delta) :
    ∃ centers : Finset T3, centers.Nonempty ∧
      let tau := temperature centers.card rho
      let p := patch gamma chi modes u centers tau
      0 < tau ∧ (∀ i, Continuous (p i)) ∧
      (∀ x, (∑ i, p i x ^ 2) = localWeight gamma chi modes u x) ∧
      (∀ x, (∑ i, p i x ^ 2 *
        lineDistanceSq (localDirection chi modes u x) (localDirection chi modes u i.1)) ≤ rho ^ 2) ∧
      ∃ c : ↑centers → FourierCoeff (Fin 3),
        (∑ i, ∫ x : T3, ‖fourierPolynomial (c i) x - (p i x : ℂ)‖ ^ 2) < delta ∧
        ‖unitTorusDerivativePhase‖ ^ 2 * (∑ i, coordinateEnergy (c i).support (c i)) ≤
          ∫ x : T3, gradientDensity gamma chi modes u rho tau x := by
  obtain ⟨centers, hc, ht, hp, hmass, hline, hfamily⟩ :=
    exists_local_gaussian_fourier_family gamma hg chi modes u hu rho hr
  exact ⟨centers, hc, ht, hp, hmass, hline, hfamily delta hd⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalGaussianFourierBudget
