import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxVariation

/-!
# Heat smoothing of the exchanged flux and its actual nonlinear source

All three input heat factors multiply. The smoothed actual source is
the variation at the smoothed velocity in the smoothed full rate. It
splits into the recomputed nonlinear source and a separate heat
commutator insertion; these two rates are not identified.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxHeatVariation

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeGalerkinKineticEnergy PancakeFilteredStrainDynamics PancakeCoefficientLimitEquation
open PeriodicGradientFluxTriple FourierVorticityPairDynamics FourierStretchingInteractionDynamics
open ExchangedFluxModeDynamics ExchangedFluxVariation FourierHeatFlow LongitudinalExchangeFluxFourier

theorem multiplier_triple (ν σ : ℝ) (p : TripleIndex) :
    multiplier ν σ p.1 * (multiplier ν σ p.2.1 * multiplier ν σ p.2.2) =
      Real.exp (-interactionDamping ν p * σ) := by
  unfold multiplier
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold interactionDamping pairDamping
  ring

theorem mixedTensor_heat (ν σ : ℝ) (u v w : FourierVelocity) (p : TripleIndex) :
    mixedTensor (coefficients ν σ u) (coefficients ν σ v) (coefficients ν σ w) p =
      Real.exp (-interactionDamping ν p * σ) • mixedTensor u v w p := by
  rw [← multiplier_triple]
  ext j i
  simp only [mixedTensor]
  simp only [fourierCurl_coefficients]
  simp only [coefficients, filteredVelocity, mixedTensor,
    coefficientCross_smul_smul, map_smul, Pi.smul_apply, smul_smul,
    RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal, smul_eq_mul]
  push_cast
  ring

theorem mixedMode_heat (ν σ : ℝ) (u v w : FourierVelocity) (p : TripleIndex) :
    mixedMode (coefficients ν σ u) (coefficients ν σ v) (coefficients ν σ w) p =
      Real.exp (-interactionDamping ν p * σ) • mixedMode u v w p := by
  simp only [mixedMode, mixedTensor_heat, map_smul]

theorem mode_heat (ν σ : ℝ) (u : FourierVelocity) (p : TripleIndex) :
    mode (coefficients ν σ u) p = Real.exp (-interactionDamping ν p * σ) • mode u p :=
  mixedMode_heat ν σ u u u p

theorem exchangeMode_heat (ν σ : ℝ) (u : FourierVelocity)
    (hu : ∀ q, modeDot q (u q) = 0) (p : TripleIndex) :
    exchangeMode (coefficients ν σ u) p =
      Real.exp (-interactionDamping ν p * σ) • exchangeMode u p := by
  rw [← mode_eq_exchangeMode _ p (coefficients_transverse ν σ u hu _) (coefficients_transverse ν σ u hu _),
    mode_heat, mode_eq_exchangeMode u p (hu _) (hu _)]

theorem variationMode_heat (ν σ : ℝ) (u v : FourierVelocity) (p : TripleIndex) :
    variationMode (coefficients ν σ u) (coefficients ν σ v) p =
      Real.exp (-interactionDamping ν p * σ) • variationMode u v p := by
  simp only [variationMode, mixedMode_heat, smul_add]

/-- The heat commutator is retained as an actual variation input. -/
theorem decayed_source_eq_resolved_add_commutator (ν σ : ℝ) (u : FourierVelocity)
    (p : TripleIndex) :
    Real.exp (-interactionDamping ν p * σ) • sourceMode u p =
      sourceMode (coefficients ν σ u) p +
        variationMode (coefficients ν σ u) (nonlinearCommutator ν σ u) p := by
  have he : coefficients ν σ (infiniteVelocityRHS 0 u) =
      infiniteVelocityRHS 0 (coefficients ν σ u) + nonlinearCommutator ν σ u := by
    unfold nonlinearCommutator
    abel
  rw [sourceMode_eq_variationMode, ← variationMode_heat, he, variationMode_add,
    ← sourceMode_eq_variationMode]

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxHeatVariation
