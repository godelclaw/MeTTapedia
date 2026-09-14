import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxHorizontalParity

/-!
# Odd horizontal data in the full heat-integrated work

Heat preserves parity. The smoothed actual inviscid tangent is even,
whereas the smoothed cubic flux is odd. Their signed pairing therefore
vanishes, including the heat/evolution commutator. This is an
instantaneous identity, not an invariant parity sector for NS evolution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StretchingFluxHeatParity

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakePeriodicVorticityEquation PancakeCoefficientLimitEquation PancakeCurlOutputTail
open PancakeHigherDerivativeMoments FullVelocityRHSReality
open StretchingFluxHorizontalParity StretchingFluxVariation StretchingFluxHeatWork
open LongitudinalGradientFlux ExchangedFluxHeatRepresentation ExchangedFluxSeriesBudget
open ExchangedFluxHeatBudget ExchangedFluxHeatAdjoint

theorem heat_coefficients_parity (ν σ : ℝ) (u : FourierVelocity) (r : ℤ)
    (hp : HasHorizontalParity r u) : HasHorizontalParity r (FourierHeatFlow.coefficients ν σ u) := by
  intro q hq
  change (FourierHeatFlow.multiplier ν σ q : ℂ) • u q = 0
  rw [hp q hq, smul_zero]

theorem inner_fluxVariation_eq_zero (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v))
    (hdu : ∀ q, modeDot q (u q) = 0) (hdv : ∀ q, modeDot q (v q) = 0)
    (hru : ∀ q, u (-q) = coefficientConjugate (u q))
    (hrv : ∀ q, v (-q) = coefficientConjugate (v q))
    (hpu : HasHorizontalParity 1 u) (hpv : HasHorizontalParity 0 v) :
    ⟪fluxVariation u v, projectedFlux 0 u⟫ = 0 := by
  rw [fluxVariation_eq_projected_variationField u v hu hv hdu hdv hru hrv, real_inner_comm]
  change ⟪gradientProjection (toTensorL2 (fluxField 0 u)),
    gradientProjection (toTensorL2 (variationField u v))⟫ = 0
  rw [inner_gradientProjection_gradientProjection]
  exact projected_variation_work_eq_zero u v hu hv hru hrv hpu hpv

theorem smoothed_inviscid_work_eq_zero {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q))
    (hp : HasHorizontalParity 1 u) :
    ⟪fluxVariation (FourierHeatFlow.coefficients ν σ u)
        (FourierHeatFlow.coefficients ν σ (infiniteVelocityRHS 0 u)),
      projectedFlux 0 (FourierHeatFlow.coefficients ν σ u)⟫ = 0 := by
  exact inner_fluxVariation_eq_zero _ _
    (FourierHeatFlow.summable_fourierMoment_coefficients hν hσ u 1
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu))
    (FourierHeatFlow.summable_fourierMoment_coefficients hν hσ _ 1
      (VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS 1 0 u hu))
    (FourierHeatFlow.coefficients_transverse ν σ u hd)
    (FourierHeatFlow.coefficients_transverse ν σ _ (infiniteVelocityRHS_transverse 0 u hd))
    (FourierHeatFlow.coefficients_reality ν σ u hr)
    (FourierHeatFlow.coefficients_reality ν σ _ (infiniteVelocityRHS_conjugate 0 u hr))
    (heat_coefficients_parity ν σ u 1 hp)
    (heat_coefficients_parity ν σ _ 0 (inviscidRHS_parity u hp))

theorem heatWorkDensity_eq_zero {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q))
    (hp : HasHorizontalParity 1 u) : heatWorkDensity ν σ u = 0 := by
  rw [heatWorkDensity, ← heat_fluxVariation_eq_resolved_add_commutator hν hσ u hu]
  exact smoothed_inviscid_work_eq_zero hν.le hσ u hu hd hr hp

theorem materialHeatWork_eq_zero {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q))
    (hp : HasHorizontalParity 1 u) : materialHeatWork ν σ u = 0 := by
  rw [← coefficientWorkDensity_eq_materialHeatWork hν.le hσ u hu hd hr,
    ← heatWorkDensity_eq_coefficientWorkDensity hν.le hσ u hu]
  exact heatWorkDensity_eq_zero hν hσ u hu hd hr hp

theorem fullGramWork_eq_zero {ν : ℝ} (hν : 0 < ν)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q))
    (hp : HasHorizontalParity 1 u) : fullGramWork ν u = 0 := by
  rw [fullGramWork_eq_integral_heatWorkDensity hν u hu hd hr]
  calc
    _ = ∫ σ : ℝ in Set.Ioi 0, (0 : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro σ hσ
      exact heatWorkDensity_eq_zero hν hσ.le u hu hd hr hp
    _ = 0 := by simp

end Mettapedia.FluidDynamics.NavierStokes.StretchingFluxHeatParity
