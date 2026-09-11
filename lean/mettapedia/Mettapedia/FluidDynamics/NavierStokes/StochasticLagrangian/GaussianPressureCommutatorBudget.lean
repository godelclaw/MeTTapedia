import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalGaussianFourierBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PhysicalPressureLocalization

/-!
# Gaussian pressure patches pay the bilinear commutator's derivative cost

The actual field chooses the cover before the Fourier tolerance, source
and receiver sets, or pressure output sets are selected. The summed
one-input commutator budget uses the existing physical gradient density.
Inverse-gap and Fourier l1 costs remain explicit; this is not a
scale- or time-uniform estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianPressureCommutatorBudget

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy PancakeQuadraticFourierSupport
open FourierEllipticProductEnergy LocalSquaredGapPressure LocalGaussianPressurePartition
open LocalGaussianGradientBudget LocalGaussianFourierBudget AdaptiveGaussianLinePartition SpectralTiltFreezing
open PhysicalPressureLocalization

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem exists_local_gaussian_commutator_budget (gamma : ℝ) (hg : 0 < gamma)
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
          (∫ x : T3, gradientDensity gamma chi modes u rho tau x) ∧
        ∀ (P K : Finset Wavevector) (v : FourierVelocity) (Q : ↑centers → Finset Wavevector),
          (∀ i, ∀ p ∈ P, ∀ k ∈ K, ∀ a ∈ (c i).support, p + k + a ∈ Q i) →
          (∑ i, ∑ q ∈ Q i,
            ‖PressureBilinearLocalization.commutatorCoefficient (localDirection chi modes u i.1)
              (c i).support P K (c i) (fourierCurl u) v q‖ ^ 2) ≤
            physicalCommutatorCost P K u v * ∫ x : T3, gradientDensity gamma chi modes u rho tau x := by
  obtain ⟨centers, hc, ht, hp, hmass, hline, hfamily⟩ :=
    exists_local_gaussian_fourier_family gamma hg chi modes u hu rho hr
  refine ⟨centers, hc, ht, hp, hmass, hline, ?_⟩
  intro delta hd
  obtain ⟨c, herr, hG⟩ := hfamily delta hd
  refine ⟨c, herr, hG, ?_⟩
  intro P K v Q hQ
  have h := sum_commutator_energy_fourierCurl_le
    (fun i : ↑centers ↦ localDirection chi modes u i.1)
    (fun i ↦ PancakeSpectralFiniteDifference.topVector_norm _)
    (fun i ↦ (c i).support) Q P K (fun i ↦ c i) u v hQ
  exact h.trans (mul_le_mul_of_nonneg_left hG (physicalCommutatorCost_nonneg P K u v))

end Mettapedia.FluidDynamics.NavierStokes.GaussianPressureCommutatorBudget
